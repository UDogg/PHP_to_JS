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
        Schema::create('offline_upload_policy', function (Blueprint $table) {
            $table->id();
            $table->string('customer_name');
            $table->string('mobile');
            $table->string('email')->nullable();
            $table->string('reg_no');
            $table->string('ic_name');
            $table->string('policy_no');
            $table->string('policy_type'); 
            $table->unsignedBigInteger('created_by');
            $table->timestamps();
            $table->softDeletes();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('offline_upload_policy');
    }
};
