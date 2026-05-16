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
        if(!Schema::hasTable('sms_activity_logs'))
        {
            Schema::create('sms_activity_logs', function (Blueprint $table) {
                $table->id();
                $table->string('mobile');
                $table->string('message');
                $table->string('type');
                $table->string('status');
                $table->string('sent_at');
                $table->timestamps();

            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('sms_activity_logs');
    }
};
