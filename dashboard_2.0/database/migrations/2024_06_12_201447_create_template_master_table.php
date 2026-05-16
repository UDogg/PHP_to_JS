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
        if(!Schema::hasTable('template_master')) {

            Schema::create('template_master', function (Blueprint $table) {
                $table->id('template_id');
                $table->string('title')->nullable();
                $table->string('alias');
                $table->enum('communication_type', ['email', 'sms', 'whatsapp']);
                $table->longText('content');
                $table->enum('status', ['Y', 'N'])->default('Y');
                $table->timestamps();
            });
        }

    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('template_master');
    }
};
