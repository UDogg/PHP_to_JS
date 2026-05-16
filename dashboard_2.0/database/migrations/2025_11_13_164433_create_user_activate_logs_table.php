<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::create('user_activate_logs', function (Blueprint $table) {
            $table->id();
            $table->unsignedBigInteger('activated_user_id');
            $table->unsignedBigInteger('activated_by');
            $table->string('recorded_ids');
            $table->timestamps();
            $table->softDeletes();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('user_activate_logs');
    }
};
